Theory vfmTest0380[no_sig_docs]
Ancestors vfmTestDefs0380
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0380_0.nsv", "result0380_1.nsv", "result0380_2.nsv", "result0380_3.nsv", "result0380_4.nsv", "result0380_5.nsv", "result0380_6.nsv", "result0380_7.nsv", "result0380_8.nsv", "result0380_9.nsv", "result0380_10.nsv", "result0380_11.nsv", "result0380_12.nsv", "result0380_13.nsv", "result0380_14.nsv", "result0380_15.nsv", "result0380_16.nsv", "result0380_17.nsv", "result0380_18.nsv", "result0380_19.nsv", "result0380_20.nsv"];
val thyn = "vfmTestDefs0380";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
