Theory vfmTest2270[no_sig_docs]
Ancestors vfmTestDefs2270
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2270_0.nsv", "result2270_1.nsv", "result2270_2.nsv", "result2270_3.nsv", "result2270_4.nsv", "result2270_5.nsv", "result2270_6.nsv", "result2270_7.nsv", "result2270_8.nsv", "result2270_9.nsv", "result2270_10.nsv", "result2270_11.nsv", "result2270_12.nsv", "result2270_13.nsv", "result2270_14.nsv", "result2270_15.nsv", "result2270_16.nsv", "result2270_17.nsv", "result2270_18.nsv", "result2270_19.nsv", "result2270_20.nsv", "result2270_21.nsv", "result2270_22.nsv", "result2270_23.nsv"];
val thyn = "vfmTestDefs2270";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
