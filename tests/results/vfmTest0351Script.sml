Theory vfmTest0351[no_sig_docs]
Ancestors vfmTestDefs0351
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0351_0.nsv", "result0351_1.nsv", "result0351_2.nsv", "result0351_3.nsv", "result0351_4.nsv", "result0351_5.nsv", "result0351_6.nsv", "result0351_7.nsv", "result0351_8.nsv", "result0351_9.nsv", "result0351_10.nsv", "result0351_11.nsv", "result0351_12.nsv", "result0351_13.nsv", "result0351_14.nsv", "result0351_15.nsv", "result0351_16.nsv", "result0351_17.nsv", "result0351_18.nsv", "result0351_19.nsv", "result0351_20.nsv", "result0351_21.nsv"];
val thyn = "vfmTestDefs0351";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
