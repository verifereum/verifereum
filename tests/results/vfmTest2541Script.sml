Theory vfmTest2541[no_sig_docs]
Ancestors vfmTestDefs2541
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2541";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
