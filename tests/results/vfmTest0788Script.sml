Theory vfmTest0788[no_sig_docs]
Ancestors vfmTestDefs0788
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0788_0.nsv", "result0788_1.nsv", "result0788_2.nsv", "result0788_3.nsv", "result0788_4.nsv", "result0788_5.nsv", "result0788_6.nsv", "result0788_7.nsv", "result0788_8.nsv", "result0788_9.nsv", "result0788_10.nsv", "result0788_11.nsv", "result0788_12.nsv", "result0788_13.nsv", "result0788_14.nsv", "result0788_15.nsv", "result0788_16.nsv", "result0788_17.nsv", "result0788_18.nsv", "result0788_19.nsv", "result0788_20.nsv", "result0788_21.nsv", "result0788_22.nsv", "result0788_23.nsv"];
val thyn = "vfmTestDefs0788";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
