Theory vfmTest1684[no_sig_docs]
Ancestors vfmTestDefs1684
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1684_0.nsv", "result1684_1.nsv", "result1684_2.nsv", "result1684_3.nsv", "result1684_4.nsv", "result1684_5.nsv", "result1684_6.nsv", "result1684_7.nsv", "result1684_8.nsv", "result1684_9.nsv", "result1684_10.nsv", "result1684_11.nsv", "result1684_12.nsv", "result1684_13.nsv", "result1684_14.nsv", "result1684_15.nsv", "result1684_16.nsv", "result1684_17.nsv", "result1684_18.nsv", "result1684_19.nsv"];
val thyn = "vfmTestDefs1684";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
