Theory vfmTest0389[no_sig_docs]
Ancestors vfmTestDefs0389
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0389_0.nsv", "result0389_1.nsv", "result0389_2.nsv", "result0389_3.nsv", "result0389_4.nsv", "result0389_5.nsv", "result0389_6.nsv", "result0389_7.nsv"];
val thyn = "vfmTestDefs0389";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
