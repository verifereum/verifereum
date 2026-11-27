Theory vfmTest1572[no_sig_docs]
Ancestors vfmTestDefs1572
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1572_0.nsv", "result1572_1.nsv", "result1572_2.nsv", "result1572_3.nsv", "result1572_4.nsv", "result1572_5.nsv", "result1572_6.nsv", "result1572_7.nsv", "result1572_8.nsv", "result1572_9.nsv", "result1572_10.nsv", "result1572_11.nsv", "result1572_12.nsv", "result1572_13.nsv", "result1572_14.nsv", "result1572_15.nsv", "result1572_16.nsv", "result1572_17.nsv", "result1572_18.nsv", "result1572_19.nsv"];
val thyn = "vfmTestDefs1572";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
