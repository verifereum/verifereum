Theory vfmTest0114[no_sig_docs]
Ancestors vfmTestDefs0114
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0114_0.nsv", "result0114_1.nsv", "result0114_2.nsv", "result0114_3.nsv", "result0114_4.nsv", "result0114_5.nsv", "result0114_6.nsv", "result0114_7.nsv", "result0114_8.nsv", "result0114_9.nsv", "result0114_10.nsv", "result0114_11.nsv", "result0114_12.nsv", "result0114_13.nsv", "result0114_14.nsv", "result0114_15.nsv", "result0114_16.nsv", "result0114_17.nsv"];
val thyn = "vfmTestDefs0114";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
