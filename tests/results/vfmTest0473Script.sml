Theory vfmTest0473[no_sig_docs]
Ancestors vfmTestDefs0473
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0473_0.nsv", "result0473_1.nsv", "result0473_2.nsv", "result0473_3.nsv", "result0473_4.nsv", "result0473_5.nsv", "result0473_6.nsv", "result0473_7.nsv", "result0473_8.nsv", "result0473_9.nsv"];
val thyn = "vfmTestDefs0473";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
