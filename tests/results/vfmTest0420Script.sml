Theory vfmTest0420[no_sig_docs]
Ancestors vfmTestDefs0420
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0420_0.nsv", "result0420_1.nsv", "result0420_2.nsv", "result0420_3.nsv", "result0420_4.nsv", "result0420_5.nsv", "result0420_6.nsv", "result0420_7.nsv", "result0420_8.nsv", "result0420_9.nsv", "result0420_10.nsv", "result0420_11.nsv", "result0420_12.nsv", "result0420_13.nsv", "result0420_14.nsv", "result0420_15.nsv", "result0420_16.nsv", "result0420_17.nsv", "result0420_18.nsv", "result0420_19.nsv", "result0420_20.nsv", "result0420_21.nsv", "result0420_22.nsv", "result0420_23.nsv", "result0420_24.nsv", "result0420_25.nsv", "result0420_26.nsv"];
val thyn = "vfmTestDefs0420";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
