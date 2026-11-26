Theory vfmTest0453[no_sig_docs]
Ancestors vfmTestDefs0453
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0453_0.nsv", "result0453_1.nsv", "result0453_2.nsv", "result0453_3.nsv", "result0453_4.nsv", "result0453_5.nsv", "result0453_6.nsv", "result0453_7.nsv", "result0453_8.nsv", "result0453_9.nsv", "result0453_10.nsv", "result0453_11.nsv"];
val thyn = "vfmTestDefs0453";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
