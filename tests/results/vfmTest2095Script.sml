Theory vfmTest2095[no_sig_docs]
Ancestors vfmTestDefs2095
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2095_0.nsv", "result2095_1.nsv", "result2095_2.nsv", "result2095_3.nsv"];
val thyn = "vfmTestDefs2095";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
