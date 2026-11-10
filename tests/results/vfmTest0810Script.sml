Theory vfmTest0810[no_sig_docs]
Ancestors vfmTestDefs0810
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0810_0.nsv", "result0810_1.nsv", "result0810_2.nsv", "result0810_3.nsv", "result0810_4.nsv", "result0810_5.nsv", "result0810_6.nsv", "result0810_7.nsv", "result0810_8.nsv", "result0810_9.nsv", "result0810_10.nsv", "result0810_11.nsv"];
val thyn = "vfmTestDefs0810";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
