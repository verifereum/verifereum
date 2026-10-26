Theory vfmTest2972[no_sig_docs]
Ancestors vfmTestDefs2972
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2972_0.nsv", "result2972_1.nsv", "result2972_2.nsv", "result2972_3.nsv", "result2972_4.nsv", "result2972_5.nsv", "result2972_6.nsv", "result2972_7.nsv", "result2972_8.nsv", "result2972_9.nsv"];
val thyn = "vfmTestDefs2972";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
