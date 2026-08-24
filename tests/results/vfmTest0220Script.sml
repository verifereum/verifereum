Theory vfmTest0220[no_sig_docs]
Ancestors vfmTestDefs0220
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0220_0.nsv", "result0220_1.nsv", "result0220_2.nsv", "result0220_3.nsv", "result0220_4.nsv", "result0220_5.nsv"];
val thyn = "vfmTestDefs0220";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
