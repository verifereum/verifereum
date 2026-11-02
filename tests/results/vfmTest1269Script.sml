Theory vfmTest1269[no_sig_docs]
Ancestors vfmTestDefs1269
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1269_0.nsv", "result1269_1.nsv", "result1269_2.nsv", "result1269_3.nsv", "result1269_4.nsv", "result1269_5.nsv", "result1269_6.nsv", "result1269_7.nsv", "result1269_8.nsv", "result1269_9.nsv", "result1269_10.nsv", "result1269_11.nsv", "result1269_12.nsv", "result1269_13.nsv", "result1269_14.nsv", "result1269_15.nsv", "result1269_16.nsv", "result1269_17.nsv", "result1269_18.nsv", "result1269_19.nsv", "result1269_20.nsv", "result1269_21.nsv"];
val thyn = "vfmTestDefs1269";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
