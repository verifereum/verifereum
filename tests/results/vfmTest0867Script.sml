Theory vfmTest0867[no_sig_docs]
Ancestors vfmTestDefs0867
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0867_0.nsv", "result0867_1.nsv", "result0867_2.nsv", "result0867_3.nsv", "result0867_4.nsv", "result0867_5.nsv", "result0867_6.nsv", "result0867_7.nsv", "result0867_8.nsv", "result0867_9.nsv", "result0867_10.nsv", "result0867_11.nsv", "result0867_12.nsv", "result0867_13.nsv", "result0867_14.nsv", "result0867_15.nsv", "result0867_16.nsv", "result0867_17.nsv", "result0867_18.nsv", "result0867_19.nsv", "result0867_20.nsv", "result0867_21.nsv", "result0867_22.nsv", "result0867_23.nsv", "result0867_24.nsv", "result0867_25.nsv"];
val thyn = "vfmTestDefs0867";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
