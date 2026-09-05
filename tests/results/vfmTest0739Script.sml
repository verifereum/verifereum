Theory vfmTest0739[no_sig_docs]
Ancestors vfmTestDefs0739
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0739_0.nsv", "result0739_1.nsv", "result0739_2.nsv", "result0739_3.nsv", "result0739_4.nsv", "result0739_5.nsv", "result0739_6.nsv", "result0739_7.nsv", "result0739_8.nsv", "result0739_9.nsv", "result0739_10.nsv", "result0739_11.nsv"];
val thyn = "vfmTestDefs0739";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
