Theory vfmTest1048[no_sig_docs]
Ancestors vfmTestDefs1048
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1048_0.nsv", "result1048_1.nsv", "result1048_2.nsv", "result1048_3.nsv"];
val thyn = "vfmTestDefs1048";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
