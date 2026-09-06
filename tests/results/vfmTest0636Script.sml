Theory vfmTest0636[no_sig_docs]
Ancestors vfmTestDefs0636
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0636_0.nsv", "result0636_1.nsv", "result0636_2.nsv", "result0636_3.nsv", "result0636_4.nsv", "result0636_5.nsv", "result0636_6.nsv", "result0636_7.nsv"];
val thyn = "vfmTestDefs0636";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
