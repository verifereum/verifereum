Theory vfmTest0708[no_sig_docs]
Ancestors vfmTestDefs0708
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0708_0.nsv", "result0708_1.nsv", "result0708_2.nsv", "result0708_3.nsv", "result0708_4.nsv", "result0708_5.nsv", "result0708_6.nsv", "result0708_7.nsv", "result0708_8.nsv", "result0708_9.nsv", "result0708_10.nsv", "result0708_11.nsv", "result0708_12.nsv", "result0708_13.nsv", "result0708_14.nsv", "result0708_15.nsv", "result0708_16.nsv", "result0708_17.nsv", "result0708_18.nsv", "result0708_19.nsv", "result0708_20.nsv", "result0708_21.nsv", "result0708_22.nsv", "result0708_23.nsv"];
val thyn = "vfmTestDefs0708";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
