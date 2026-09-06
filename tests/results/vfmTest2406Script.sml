Theory vfmTest2406[no_sig_docs]
Ancestors vfmTestDefs2406
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2406_0.nsv", "result2406_1.nsv", "result2406_2.nsv", "result2406_3.nsv", "result2406_4.nsv", "result2406_5.nsv", "result2406_6.nsv", "result2406_7.nsv", "result2406_8.nsv", "result2406_9.nsv", "result2406_10.nsv", "result2406_11.nsv", "result2406_12.nsv", "result2406_13.nsv", "result2406_14.nsv", "result2406_15.nsv"];
val thyn = "vfmTestDefs2406";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
