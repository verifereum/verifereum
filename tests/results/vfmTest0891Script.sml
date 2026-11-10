Theory vfmTest0891[no_sig_docs]
Ancestors vfmTestDefs0891
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0891_0.nsv", "result0891_1.nsv", "result0891_2.nsv", "result0891_3.nsv", "result0891_4.nsv", "result0891_5.nsv", "result0891_6.nsv", "result0891_7.nsv", "result0891_8.nsv", "result0891_9.nsv", "result0891_10.nsv", "result0891_11.nsv", "result0891_12.nsv"];
val thyn = "vfmTestDefs0891";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
