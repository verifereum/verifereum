Theory vfmTest2280[no_sig_docs]
Ancestors vfmTestDefs2280
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2280_0.nsv", "result2280_1.nsv"];
val thyn = "vfmTestDefs2280";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
