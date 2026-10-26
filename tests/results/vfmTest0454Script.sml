Theory vfmTest0454[no_sig_docs]
Ancestors vfmTestDefs0454
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0454_0.nsv", "result0454_1.nsv", "result0454_2.nsv", "result0454_3.nsv", "result0454_4.nsv", "result0454_5.nsv", "result0454_6.nsv", "result0454_7.nsv", "result0454_8.nsv", "result0454_9.nsv", "result0454_10.nsv", "result0454_11.nsv", "result0454_12.nsv", "result0454_13.nsv", "result0454_14.nsv", "result0454_15.nsv", "result0454_16.nsv", "result0454_17.nsv", "result0454_18.nsv", "result0454_19.nsv", "result0454_20.nsv", "result0454_21.nsv", "result0454_22.nsv", "result0454_23.nsv"];
val thyn = "vfmTestDefs0454";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
