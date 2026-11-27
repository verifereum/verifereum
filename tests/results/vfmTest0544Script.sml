Theory vfmTest0544[no_sig_docs]
Ancestors vfmTestDefs0544
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0544_0.nsv", "result0544_1.nsv", "result0544_2.nsv", "result0544_3.nsv", "result0544_4.nsv", "result0544_5.nsv", "result0544_6.nsv", "result0544_7.nsv", "result0544_8.nsv", "result0544_9.nsv", "result0544_10.nsv", "result0544_11.nsv", "result0544_12.nsv", "result0544_13.nsv", "result0544_14.nsv", "result0544_15.nsv", "result0544_16.nsv", "result0544_17.nsv", "result0544_18.nsv", "result0544_19.nsv", "result0544_20.nsv", "result0544_21.nsv", "result0544_22.nsv", "result0544_23.nsv", "result0544_24.nsv", "result0544_25.nsv", "result0544_26.nsv", "result0544_27.nsv", "result0544_28.nsv", "result0544_29.nsv", "result0544_30.nsv", "result0544_31.nsv"];
val thyn = "vfmTestDefs0544";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
