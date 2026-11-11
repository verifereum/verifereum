Theory vfmTest0177[no_sig_docs]
Ancestors vfmTestDefs0177
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0177_0.nsv", "result0177_1.nsv", "result0177_2.nsv", "result0177_3.nsv", "result0177_4.nsv", "result0177_5.nsv", "result0177_6.nsv", "result0177_7.nsv", "result0177_8.nsv", "result0177_9.nsv", "result0177_10.nsv", "result0177_11.nsv", "result0177_12.nsv", "result0177_13.nsv", "result0177_14.nsv", "result0177_15.nsv", "result0177_16.nsv", "result0177_17.nsv", "result0177_18.nsv", "result0177_19.nsv", "result0177_20.nsv", "result0177_21.nsv", "result0177_22.nsv", "result0177_23.nsv", "result0177_24.nsv", "result0177_25.nsv", "result0177_26.nsv", "result0177_27.nsv", "result0177_28.nsv", "result0177_29.nsv", "result0177_30.nsv", "result0177_31.nsv"];
val thyn = "vfmTestDefs0177";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
