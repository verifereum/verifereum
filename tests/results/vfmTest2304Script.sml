Theory vfmTest2304[no_sig_docs]
Ancestors vfmTestDefs2304
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2304_0.nsv", "result2304_1.nsv", "result2304_2.nsv", "result2304_3.nsv", "result2304_4.nsv", "result2304_5.nsv", "result2304_6.nsv", "result2304_7.nsv", "result2304_8.nsv"];
val thyn = "vfmTestDefs2304";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
