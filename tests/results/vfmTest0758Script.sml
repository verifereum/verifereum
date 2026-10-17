Theory vfmTest0758[no_sig_docs]
Ancestors vfmTestDefs0758
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0758_0.nsv", "result0758_1.nsv", "result0758_2.nsv", "result0758_3.nsv", "result0758_4.nsv", "result0758_5.nsv", "result0758_6.nsv", "result0758_7.nsv", "result0758_8.nsv", "result0758_9.nsv", "result0758_10.nsv", "result0758_11.nsv", "result0758_12.nsv", "result0758_13.nsv", "result0758_14.nsv", "result0758_15.nsv", "result0758_16.nsv", "result0758_17.nsv", "result0758_18.nsv", "result0758_19.nsv", "result0758_20.nsv", "result0758_21.nsv", "result0758_22.nsv", "result0758_23.nsv", "result0758_24.nsv", "result0758_25.nsv", "result0758_26.nsv", "result0758_27.nsv", "result0758_28.nsv", "result0758_29.nsv", "result0758_30.nsv", "result0758_31.nsv", "result0758_32.nsv", "result0758_33.nsv", "result0758_34.nsv", "result0758_35.nsv"];
val thyn = "vfmTestDefs0758";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
