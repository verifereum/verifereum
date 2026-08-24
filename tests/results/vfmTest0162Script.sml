Theory vfmTest0162[no_sig_docs]
Ancestors vfmTestDefs0162
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0162_0.nsv", "result0162_1.nsv", "result0162_2.nsv", "result0162_3.nsv", "result0162_4.nsv", "result0162_5.nsv", "result0162_6.nsv", "result0162_7.nsv", "result0162_8.nsv", "result0162_9.nsv", "result0162_10.nsv", "result0162_11.nsv"];
val thyn = "vfmTestDefs0162";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
