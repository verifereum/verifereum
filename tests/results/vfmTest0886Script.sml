Theory vfmTest0886[no_sig_docs]
Ancestors vfmTestDefs0886
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0886_0.nsv"];
val thyn = "vfmTestDefs0886";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
