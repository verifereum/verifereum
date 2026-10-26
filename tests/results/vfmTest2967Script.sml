Theory vfmTest2967[no_sig_docs]
Ancestors vfmTestDefs2967
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2967_0.nsv", "result2967_1.nsv", "result2967_2.nsv", "result2967_3.nsv", "result2967_4.nsv", "result2967_5.nsv", "result2967_6.nsv", "result2967_7.nsv", "result2967_8.nsv"];
val thyn = "vfmTestDefs2967";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
