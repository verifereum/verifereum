Theory vfmTest0020[no_sig_docs]
Ancestors vfmTestDefs0020
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0020_0.nsv", "result0020_1.nsv", "result0020_2.nsv", "result0020_3.nsv", "result0020_4.nsv", "result0020_5.nsv", "result0020_6.nsv", "result0020_7.nsv", "result0020_8.nsv", "result0020_9.nsv", "result0020_10.nsv", "result0020_11.nsv", "result0020_12.nsv", "result0020_13.nsv", "result0020_14.nsv", "result0020_15.nsv", "result0020_16.nsv", "result0020_17.nsv", "result0020_18.nsv", "result0020_19.nsv", "result0020_20.nsv", "result0020_21.nsv", "result0020_22.nsv", "result0020_23.nsv", "result0020_24.nsv", "result0020_25.nsv", "result0020_26.nsv", "result0020_27.nsv", "result0020_28.nsv", "result0020_29.nsv"];
val thyn = "vfmTestDefs0020";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
