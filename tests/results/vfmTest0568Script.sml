Theory vfmTest0568[no_sig_docs]
Ancestors vfmTestDefs0568
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0568_0.nsv", "result0568_1.nsv", "result0568_2.nsv", "result0568_3.nsv", "result0568_4.nsv", "result0568_5.nsv", "result0568_6.nsv", "result0568_7.nsv", "result0568_8.nsv", "result0568_9.nsv"];
val thyn = "vfmTestDefs0568";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
