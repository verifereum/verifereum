Theory vfmTest0644[no_sig_docs]
Ancestors vfmTestDefs0644
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0644_0.nsv", "result0644_1.nsv", "result0644_2.nsv", "result0644_3.nsv", "result0644_4.nsv", "result0644_5.nsv", "result0644_6.nsv", "result0644_7.nsv", "result0644_8.nsv", "result0644_9.nsv", "result0644_10.nsv", "result0644_11.nsv", "result0644_12.nsv", "result0644_13.nsv", "result0644_14.nsv", "result0644_15.nsv", "result0644_16.nsv", "result0644_17.nsv", "result0644_18.nsv", "result0644_19.nsv", "result0644_20.nsv", "result0644_21.nsv", "result0644_22.nsv", "result0644_23.nsv", "result0644_24.nsv", "result0644_25.nsv", "result0644_26.nsv", "result0644_27.nsv", "result0644_28.nsv", "result0644_29.nsv"];
val thyn = "vfmTestDefs0644";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
