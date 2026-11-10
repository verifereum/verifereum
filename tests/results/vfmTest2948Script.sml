Theory vfmTest2948[no_sig_docs]
Ancestors vfmTestDefs2948
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2948_0.nsv", "result2948_1.nsv", "result2948_2.nsv", "result2948_3.nsv", "result2948_4.nsv", "result2948_5.nsv"];
val thyn = "vfmTestDefs2948";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
