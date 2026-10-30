Theory vfmTest0892[no_sig_docs]
Ancestors vfmTestDefs0892
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0892_0.nsv", "result0892_1.nsv", "result0892_2.nsv", "result0892_3.nsv", "result0892_4.nsv", "result0892_5.nsv", "result0892_6.nsv", "result0892_7.nsv", "result0892_8.nsv", "result0892_9.nsv", "result0892_10.nsv", "result0892_11.nsv", "result0892_12.nsv", "result0892_13.nsv"];
val thyn = "vfmTestDefs0892";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
