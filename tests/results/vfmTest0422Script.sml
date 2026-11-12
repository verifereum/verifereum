Theory vfmTest0422[no_sig_docs]
Ancestors vfmTestDefs0422
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0422_0.nsv", "result0422_1.nsv", "result0422_2.nsv", "result0422_3.nsv", "result0422_4.nsv", "result0422_5.nsv", "result0422_6.nsv", "result0422_7.nsv", "result0422_8.nsv", "result0422_9.nsv", "result0422_10.nsv", "result0422_11.nsv", "result0422_12.nsv", "result0422_13.nsv", "result0422_14.nsv", "result0422_15.nsv", "result0422_16.nsv", "result0422_17.nsv", "result0422_18.nsv", "result0422_19.nsv", "result0422_20.nsv", "result0422_21.nsv", "result0422_22.nsv", "result0422_23.nsv", "result0422_24.nsv", "result0422_25.nsv", "result0422_26.nsv"];
val thyn = "vfmTestDefs0422";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
