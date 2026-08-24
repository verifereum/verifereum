Theory vfmTest0367[no_sig_docs]
Ancestors vfmTestDefs0367
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0367_0.nsv", "result0367_1.nsv", "result0367_2.nsv", "result0367_3.nsv", "result0367_4.nsv", "result0367_5.nsv", "result0367_6.nsv", "result0367_7.nsv", "result0367_8.nsv", "result0367_9.nsv", "result0367_10.nsv", "result0367_11.nsv", "result0367_12.nsv", "result0367_13.nsv", "result0367_14.nsv", "result0367_15.nsv", "result0367_16.nsv", "result0367_17.nsv", "result0367_18.nsv", "result0367_19.nsv", "result0367_20.nsv", "result0367_21.nsv", "result0367_22.nsv", "result0367_23.nsv", "result0367_24.nsv", "result0367_25.nsv", "result0367_26.nsv", "result0367_27.nsv", "result0367_28.nsv", "result0367_29.nsv"];
val thyn = "vfmTestDefs0367";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
