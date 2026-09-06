Theory vfmTest0022[no_sig_docs]
Ancestors vfmTestDefs0022
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0022_0.nsv", "result0022_1.nsv", "result0022_2.nsv", "result0022_3.nsv", "result0022_4.nsv", "result0022_5.nsv", "result0022_6.nsv", "result0022_7.nsv", "result0022_8.nsv", "result0022_9.nsv", "result0022_10.nsv", "result0022_11.nsv", "result0022_12.nsv"];
val thyn = "vfmTestDefs0022";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
