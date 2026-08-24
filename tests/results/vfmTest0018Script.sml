Theory vfmTest0018[no_sig_docs]
Ancestors vfmTestDefs0018
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0018_0.nsv", "result0018_1.nsv", "result0018_2.nsv", "result0018_3.nsv", "result0018_4.nsv", "result0018_5.nsv"];
val thyn = "vfmTestDefs0018";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
