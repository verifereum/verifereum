Theory vfmTest2100[no_sig_docs]
Ancestors vfmTestDefs2100
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2100_0.nsv", "result2100_1.nsv", "result2100_2.nsv", "result2100_3.nsv", "result2100_4.nsv", "result2100_5.nsv", "result2100_6.nsv", "result2100_7.nsv", "result2100_8.nsv", "result2100_9.nsv", "result2100_10.nsv", "result2100_11.nsv", "result2100_12.nsv", "result2100_13.nsv", "result2100_14.nsv", "result2100_15.nsv"];
val thyn = "vfmTestDefs2100";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
