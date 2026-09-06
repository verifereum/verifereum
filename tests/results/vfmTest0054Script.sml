Theory vfmTest0054[no_sig_docs]
Ancestors vfmTestDefs0054
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0054_0.nsv", "result0054_1.nsv", "result0054_2.nsv", "result0054_3.nsv", "result0054_4.nsv", "result0054_5.nsv", "result0054_6.nsv", "result0054_7.nsv", "result0054_8.nsv", "result0054_9.nsv", "result0054_10.nsv", "result0054_11.nsv", "result0054_12.nsv", "result0054_13.nsv", "result0054_14.nsv", "result0054_15.nsv", "result0054_16.nsv", "result0054_17.nsv", "result0054_18.nsv", "result0054_19.nsv", "result0054_20.nsv", "result0054_21.nsv", "result0054_22.nsv", "result0054_23.nsv", "result0054_24.nsv", "result0054_25.nsv", "result0054_26.nsv", "result0054_27.nsv", "result0054_28.nsv", "result0054_29.nsv"];
val thyn = "vfmTestDefs0054";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
