Theory vfmTest0717[no_sig_docs]
Ancestors vfmTestDefs0717
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0717_0.nsv", "result0717_1.nsv", "result0717_2.nsv", "result0717_3.nsv", "result0717_4.nsv", "result0717_5.nsv", "result0717_6.nsv", "result0717_7.nsv", "result0717_8.nsv"];
val thyn = "vfmTestDefs0717";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
