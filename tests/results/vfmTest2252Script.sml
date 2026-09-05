Theory vfmTest2252[no_sig_docs]
Ancestors vfmTestDefs2252
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2252_0.nsv", "result2252_1.nsv", "result2252_2.nsv", "result2252_3.nsv", "result2252_4.nsv", "result2252_5.nsv", "result2252_6.nsv", "result2252_7.nsv", "result2252_8.nsv", "result2252_9.nsv", "result2252_10.nsv"];
val thyn = "vfmTestDefs2252";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
