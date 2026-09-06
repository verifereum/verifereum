Theory vfmTest0169[no_sig_docs]
Ancestors vfmTestDefs0169
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0169_0.nsv", "result0169_1.nsv", "result0169_2.nsv", "result0169_3.nsv", "result0169_4.nsv", "result0169_5.nsv", "result0169_6.nsv", "result0169_7.nsv", "result0169_8.nsv", "result0169_9.nsv", "result0169_10.nsv", "result0169_11.nsv", "result0169_12.nsv", "result0169_13.nsv", "result0169_14.nsv", "result0169_15.nsv", "result0169_16.nsv", "result0169_17.nsv", "result0169_18.nsv", "result0169_19.nsv", "result0169_20.nsv", "result0169_21.nsv", "result0169_22.nsv", "result0169_23.nsv", "result0169_24.nsv", "result0169_25.nsv", "result0169_26.nsv", "result0169_27.nsv", "result0169_28.nsv", "result0169_29.nsv", "result0169_30.nsv", "result0169_31.nsv"];
val thyn = "vfmTestDefs0169";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
