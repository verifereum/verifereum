Theory vfmTest2400[no_sig_docs]
Ancestors vfmTestDefs2400
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2400_0.nsv", "result2400_1.nsv", "result2400_2.nsv", "result2400_3.nsv", "result2400_4.nsv", "result2400_5.nsv", "result2400_6.nsv", "result2400_7.nsv", "result2400_8.nsv", "result2400_9.nsv", "result2400_10.nsv", "result2400_11.nsv", "result2400_12.nsv", "result2400_13.nsv", "result2400_14.nsv", "result2400_15.nsv", "result2400_16.nsv", "result2400_17.nsv", "result2400_18.nsv", "result2400_19.nsv"];
val thyn = "vfmTestDefs2400";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
