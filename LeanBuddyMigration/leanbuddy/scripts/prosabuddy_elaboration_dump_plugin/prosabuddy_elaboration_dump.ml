open Fleche

let target_env = "PROSABUDDY_ELAB_TARGETS"
let output_env = "PROSABUDDY_ELAB_OUTPUT"

let split_targets value =
  value
  |> String.split_on_char ','
  |> List.map String.trim
  |> List.filter (fun item -> not (String.equal item ""))

let required_env name =
  match Sys.getenv_opt name with
  | Some value when not (String.equal (String.trim value) "") -> value
  | _ -> failwith (Printf.sprintf "required environment variable %s is missing" name)

let universes_to_yojson = function
  | Declarations.Monomorphic -> `Assoc [ ("kind", `String "Monomorphic") ]
  | Declarations.Polymorphic context ->
    `Assoc
      [ ("kind", `String "Polymorphic")
      ; ("context", Serlib.Ser_uvars.AbstractContext.to_yojson context)
      ]

let body_to_yojson = function
  | Declarations.Undef inline ->
    `Assoc
      [ ("kind", `String "Undef")
      ; ( "inline"
        , match inline with None -> `Null | Some level -> `Int level )
      ; ("term", `Null)
      ]
  | Declarations.Def term ->
    `Assoc
      [ ("kind", `String "Transparent")
      ; ("term", Serlib.Ser_constr.constr_to_yojson term)
      ]
  | Declarations.OpaqueDef _ ->
    `Assoc [ ("kind", `String "Opaque"); ("term", `Null) ]
  | Declarations.Primitive _ ->
    `Assoc [ ("kind", `String "Primitive"); ("term", `Null) ]
  | Declarations.Symbol _ ->
    `Assoc [ ("kind", `String "Symbol"); ("term", `Null) ]

let pretty_type env typ =
  let sigma = Evd.from_env env in
  Printer.pr_constr_env env sigma typ |> Pp.string_of_ppcmds

let dump_constant target =
  try
    let qualid = Libnames.qualid_of_string target in
    let constant = Nametab.locate_constant qualid in
    let body = Global.lookup_constant constant in
    let env = Global.env () in
    `Assoc
      [ ("requested_name", `String target)
      ; ("resolved_name", `String (Names.Constant.to_string constant))
      ; ("kind", `String "constant")
      ; ("pretty_type", `String (pretty_type env body.Declarations.const_type))
      ; ("type", Serlib.Ser_constr.types_to_yojson body.Declarations.const_type)
      ; ("hyps", Serlib.Ser_constr.named_context_to_yojson body.Declarations.const_hyps)
      ; ("universe_hypotheses", Serlib.Ser_uvars.Instance.to_yojson body.Declarations.const_univ_hyps)
      ; ("universes", universes_to_yojson body.Declarations.const_universes)
      ; ("relevance", Serlib.Ser_sorts.relevance_to_yojson body.Declarations.const_relevance)
      ; ("typing_flags", Serlib.Ser_declarations.typing_flags_to_yojson body.Declarations.const_typing_flags)
      ; ("body", body_to_yojson body.Declarations.const_body)
      ; ("raw_declaration", Serlib.Ser_declarations.constant_body_to_yojson body)
      ]
  with exn ->
    `Assoc
      [ ("requested_name", `String target)
      ; ("error", `String (Printexc.to_string exn))
      ]

let extraction_json ~source targets =
  `Assoc
    [ ("schema_version", `Int 1)
    ; ("source", `String source)
    ; ("targets", `List (List.map dump_constant targets))
    ]

let write_json path json =
  let channel = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr channel)
    (fun () ->
      Yojson.Safe.pretty_to_channel channel json;
      output_char channel '\n')

let report_error ~io message =
  Io.Report.msg ~io ~lvl:Io.Level.Error "[elaboration-dump] %s" message

let dump_elaboration ~io ~token ~(doc : Doc.t) =
  try
    let targets = required_env target_env |> split_targets in
    if targets = [] then failwith "no target names were provided";
    let output = required_env output_env in
    let source = Lang.LUri.File.to_string_file doc.uri in
    match List.rev doc.nodes with
    | [] -> report_error ~io "document has no completed nodes"
    | final_node :: _ ->
      let result =
        Coq.State.in_state
          ~token
          ~st:final_node.state
          ~f:(fun () -> extraction_json ~source targets)
          ()
      in
      (match result with
       | Coq.Protect.{ E.r = R.Completed (Ok json); feedback = _ } ->
         write_json output json;
         Io.Report.msg
           ~io
           ~lvl:Io.Level.Info
           "[elaboration-dump] wrote %d target(s) to %s"
           (List.length targets)
           output
       | Coq.Protect.{ E.r = R.Completed (Error (Anomaly { msg; _ })); feedback = _ }
       | Coq.Protect.{ E.r = R.Completed (Error (User { msg; _ })); feedback = _ } ->
         report_error ~io (Pp.string_of_ppcmds msg)
       | Coq.Protect.{ E.r = R.Interrupted; feedback = _ } ->
         report_error ~io "state query was interrupted")
  with exn -> report_error ~io (Printexc.to_string exn)

let () = Theory.Register.Completed.add dump_elaboration
