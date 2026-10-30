Theory vfmTest2952[no_sig_docs]
Ancestors vfmTestDefs2952
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2952_0.nsv", "result2952_1.nsv", "result2952_2.nsv", "result2952_3.nsv", "result2952_4.nsv", "result2952_5.nsv"];
val thyn = "vfmTestDefs2952";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
