Theory vfmTest0023[no_sig_docs]
Ancestors vfmTestDefs0023
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0023_0.nsv", "result0023_1.nsv", "result0023_2.nsv", "result0023_3.nsv", "result0023_4.nsv", "result0023_5.nsv", "result0023_6.nsv", "result0023_7.nsv", "result0023_8.nsv", "result0023_9.nsv", "result0023_10.nsv", "result0023_11.nsv", "result0023_12.nsv", "result0023_13.nsv"];
val thyn = "vfmTestDefs0023";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
