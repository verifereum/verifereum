Theory vfmTest0541[no_sig_docs]
Ancestors vfmTestDefs0541
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0541";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
