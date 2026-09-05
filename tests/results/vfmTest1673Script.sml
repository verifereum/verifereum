Theory vfmTest1673[no_sig_docs]
Ancestors vfmTestDefs1673
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1673_0.nsv", "result1673_1.nsv", "result1673_2.nsv", "result1673_3.nsv", "result1673_4.nsv", "result1673_5.nsv", "result1673_6.nsv", "result1673_7.nsv", "result1673_8.nsv", "result1673_9.nsv", "result1673_10.nsv", "result1673_11.nsv", "result1673_12.nsv", "result1673_13.nsv", "result1673_14.nsv", "result1673_15.nsv", "result1673_16.nsv", "result1673_17.nsv", "result1673_18.nsv", "result1673_19.nsv"];
val thyn = "vfmTestDefs1673";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
