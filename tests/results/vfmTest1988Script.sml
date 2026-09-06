Theory vfmTest1988[no_sig_docs]
Ancestors vfmTestDefs1988
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1988_0.nsv", "result1988_1.nsv", "result1988_2.nsv", "result1988_3.nsv"];
val thyn = "vfmTestDefs1988";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
