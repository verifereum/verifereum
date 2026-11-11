Theory vfmTest1533[no_sig_docs]
Ancestors vfmTestDefs1533
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1533_0.nsv", "result1533_1.nsv", "result1533_2.nsv", "result1533_3.nsv", "result1533_4.nsv", "result1533_5.nsv", "result1533_6.nsv", "result1533_7.nsv", "result1533_8.nsv", "result1533_9.nsv", "result1533_10.nsv", "result1533_11.nsv", "result1533_12.nsv", "result1533_13.nsv", "result1533_14.nsv", "result1533_15.nsv", "result1533_16.nsv", "result1533_17.nsv", "result1533_18.nsv", "result1533_19.nsv"];
val thyn = "vfmTestDefs1533";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
