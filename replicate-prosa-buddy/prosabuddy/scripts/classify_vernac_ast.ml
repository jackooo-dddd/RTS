(* Annotate coq-lsp astdump JSONL records with Rocq's official vernacular
   classification.  The original AST is retained because the policy validator
   must compare theorem declarations and commands outside the target proof. *)

open Vernacextend
open Vernacexpr

let json_string value = `String value

let json_option f = function
  | Some value -> f value
  | None -> `Null

let json_list f values = `List (List.map f values)

let string_of_when = function
  | VtNow -> "Now"
  | VtLater -> "Later"

let string_of_opacity = function
  | GuaranteesOpacity -> "GuaranteesOpacity"
  | Doesn'tGuaranteeOpacity -> "DoesntGuaranteeOpacity"

let string_of_qed = function
  | VtKeep VtKeepAxiom -> "KeepAxiom"
  | VtKeep VtKeepDefined -> "KeepDefined"
  | VtKeep VtKeepOpaque -> "KeepOpaque"
  | VtDrop -> "Drop"

let classification_fields classification =
  let category, names, when_, opacity, qed_action, proof_block =
    match classification with
    | VtStartProof (opacity, names) ->
      ( "StartProof"
      , List.map Names.Id.to_string names
      , None
      , Some (string_of_opacity opacity)
      , None
      , None )
    | VtSideff (names, when_) ->
      ( "Sideff"
      , List.map Names.Id.to_string names
      , Some (string_of_when when_)
      , None
      , None
      , None )
    | VtQed qed_action ->
      ("Qed", [], None, None, Some (string_of_qed qed_action), None)
    | VtProofStep { proof_block_detection } ->
      ("ProofStep", [], None, None, None, proof_block_detection)
    | VtQuery -> ("Query", [], None, None, None, None)
    | VtProofMode _ -> ("ProofMode", [], None, None, None, None)
    | VtMeta -> ("Meta", [], None, None, None, None)
  in
  [ ("classification", json_string (Vernac_classifier.string_of_vernac_classification classification))
  ; ("category", json_string category)
  ; ("names", json_list json_string names)
  ; ("when", json_option json_string when_)
  ; ("opacity_guarantee", json_option json_string opacity)
  ; ("qed_action", json_option json_string qed_action)
  ; ("proof_block_detection", json_option json_string proof_block)
  ]

let member name json = Yojson.Safe.Util.member name json

let phase_and_kind json =
  match member "expr" (member "v" json) with
  | `List [ `String phase; `List (`String kind :: _) ] -> (phase, kind)
  | _ -> ("<unknown>", "<unknown>")

let location_fields json =
  let loc = member "loc" json in
  [ ("source_line", member "line_nb" loc)
  ; ("source_end_line", member "line_nb_last" loc)
  ; ("byte_start", member "bp" loc)
  ; ("byte_end", member "ep" loc)
  ]

let string_of_control = function
  | ControlTime -> "Time"
  | ControlInstructions -> "Instructions"
  | ControlProfile _ -> "Profile"
  | ControlRedirect _ -> "Redirect"
  | ControlTimeout _ -> "Timeout"
  | ControlFail -> "Fail"
  | ControlSucceed -> "Succeed"

let string_of_export = function
  | Lib.Import -> "Import"
  | Lib.Export -> "Export"

let string_of_import_filter = function
  | ImportAll -> "All"
  | ImportNames _ -> "Names"

let attribute_name ({ CAst.v = name, _; _ } : Attributes.vernac_flag) = name

let require_json from export modules =
  let mode, has_categories =
    match export with
    | None -> ("Require", false)
    | Some (export, categories) ->
      (string_of_export export, match categories with Some _ -> true | None -> false)
  in
  let module_json (module_name, filter) =
    `Assoc
      [ ("name", json_string (Libnames.string_of_qualid module_name))
      ; ("filter", json_string (string_of_import_filter filter))
      ]
  in
  `Assoc
    [ ("from", json_option (fun value -> json_string (Libnames.string_of_qualid value)) from)
    ; ("mode", json_string mode)
    ; ("has_categories", `Bool has_categories)
    ; ("modules", json_list module_json modules)
    ]

let extension_json extension =
  `Assoc
    [ ("plugin", json_string extension.ext_plugin)
    ; ("entry", json_string extension.ext_entry)
    ; ("index", `Int extension.ext_index)
    ]

let proof_end_json = function
  | VernacSynPure (VernacEndProof Admitted) ->
    Some (`Assoc [ ("kind", json_string "Admitted"); ("name", `Null) ])
  | VernacSynPure (VernacEndProof (Proved (Opaque, name))) ->
    Some
      (`Assoc
        [ ("kind", json_string "Opaque")
        ; ("name", json_option (fun value -> json_string (Names.Id.to_string value.CAst.v)) name)
        ])
  | VernacSynPure (VernacEndProof (Proved (Transparent, name))) ->
    Some
      (`Assoc
        [ ("kind", json_string "Transparent")
        ; ("name", json_option (fun value -> json_string (Names.Id.to_string value.CAst.v)) name)
        ])
  | VernacSynPure (VernacExactProof _) ->
    Some (`Assoc [ ("kind", json_string "ExactProof"); ("name", `Null) ])
  | VernacSynPure VernacAbort ->
    Some (`Assoc [ ("kind", json_string "Abort"); ("name", `Null) ])
  | _ -> None

let command_metadata ({ CAst.v = command; _ } : vernac_control) =
  let require, extension =
    match command.expr with
    | VernacSynterp (VernacRequire (from, export, modules)) ->
      (Some (require_json from export modules), None)
    | VernacSynterp (VernacExtend (extension, _)) ->
      (None, Some (extension_json extension))
    | _ -> (None, None)
  in
  [ ("controls", json_list (fun value -> json_string (string_of_control value)) command.control)
  ; ("attributes", json_list (fun value -> json_string (attribute_name value)) command.attrs)
  ; ("require", json_option (fun value -> value) require)
  ; ("extension", json_option (fun value -> value) extension)
  ; ("proof_end", json_option (fun value -> value) (proof_end_json command.expr))
  ]

let add_count counts category =
  let previous =
    match Hashtbl.find_opt counts category with
    | Some count -> count
    | None -> 0
  in
  Hashtbl.replace counts category (previous + 1)

let classify_line ~index json =
  match Serlib.Ser_vernacexpr.vernac_control_of_yojson json with
  | Error message ->
    Error
      (`Assoc
        ([ ("schema_version", `Int 1)
         ; ("index", `Int index)
         ; ("error", json_string message)
         ; ("ast", json)
         ]
        @ location_fields json))
  | Ok vernac ->
    try
      let classification = Vernac_classifier.classify_vernac vernac in
      let phase, kind = phase_and_kind json in
      Ok
        (`Assoc
          ([ ("schema_version", `Int 1)
           ; ("index", `Int index)
           ; ("phase", json_string phase)
           ; ("vernac_kind", json_string kind)
           ; ("ast", json)
           ]
          @ location_fields json
          @ command_metadata vernac
          @ classification_fields classification))
    with exn ->
      Error
        (`Assoc
          ([ ("schema_version", `Int 1)
           ; ("index", `Int index)
           ; ("error", json_string (Printexc.to_string exn))
           ; ("ast", json)
           ]
          @ location_fields json))

let () =
  if Array.length Sys.argv <> 3 then begin
    prerr_endline "usage: classify_vernac_ast INPUT.jsonl.astdump OUTPUT.classified.jsonl";
    exit 64
  end;
  let input_path = Sys.argv.(1) in
  let output_path = Sys.argv.(2) in
  let input = open_in input_path in
  let output = open_out output_path in
  let counts = Hashtbl.create 11 in
  let errors = ref 0 in
  let rec loop index =
    match input_line input with
    | line ->
      if String.trim line = "" then loop index
      else begin
        let result =
          try classify_line ~index (Yojson.Safe.from_string line)
          with exn ->
            Error
              (`Assoc
                [ ("schema_version", `Int 1)
                ; ("index", `Int index)
                ; ("error", json_string (Printexc.to_string exn))
                ])
        in
        let record =
          match result with
          | Ok (`Assoc fields as record) ->
            let category =
              match List.assoc_opt "category" fields with
              | Some (`String value) -> value
              | _ -> "<unknown>"
            in
            add_count counts category;
            record
          | Ok record -> record
          | Error record ->
            incr errors;
            add_count counts "Error";
            record
        in
        Yojson.Safe.to_channel output record;
        output_char output '\n';
        loop (index + 1)
      end
    | exception End_of_file -> ()
  in
  Fun.protect
    ~finally:(fun () -> close_in_noerr input; close_out_noerr output)
    (fun () -> loop 1);
  Hashtbl.to_seq counts
  |> List.of_seq
  |> List.sort (fun (left, _) (right, _) -> String.compare left right)
  |> List.iter (fun (category, count) -> Printf.printf "%s\t%d\n" category count);
  Printf.printf "Total\t%d\n" (Hashtbl.to_seq_values counts |> Seq.fold_left ( + ) 0);
  if !errors <> 0 then exit 2
