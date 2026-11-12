Theory vfmTest0424[no_sig_docs]
Ancestors vfmTestDefs0424
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0424_0.nsv", "result0424_1.nsv", "result0424_2.nsv", "result0424_3.nsv", "result0424_4.nsv", "result0424_5.nsv", "result0424_6.nsv", "result0424_7.nsv", "result0424_8.nsv", "result0424_9.nsv", "result0424_10.nsv", "result0424_11.nsv", "result0424_12.nsv", "result0424_13.nsv", "result0424_14.nsv", "result0424_15.nsv", "result0424_16.nsv", "result0424_17.nsv", "result0424_18.nsv", "result0424_19.nsv", "result0424_20.nsv", "result0424_21.nsv", "result0424_22.nsv", "result0424_23.nsv", "result0424_24.nsv", "result0424_25.nsv", "result0424_26.nsv"];
val thyn = "vfmTestDefs0424";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
