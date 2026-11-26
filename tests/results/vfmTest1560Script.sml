Theory vfmTest1560[no_sig_docs]
Ancestors vfmTestDefs1560
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1560_0.nsv", "result1560_1.nsv", "result1560_2.nsv", "result1560_3.nsv", "result1560_4.nsv", "result1560_5.nsv", "result1560_6.nsv", "result1560_7.nsv", "result1560_8.nsv", "result1560_9.nsv", "result1560_10.nsv", "result1560_11.nsv", "result1560_12.nsv", "result1560_13.nsv", "result1560_14.nsv", "result1560_15.nsv", "result1560_16.nsv", "result1560_17.nsv", "result1560_18.nsv", "result1560_19.nsv"];
val thyn = "vfmTestDefs1560";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
