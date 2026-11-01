Theory vfmTest1357[no_sig_docs]
Ancestors vfmTestDefs1357
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1357_0.nsv", "result1357_1.nsv", "result1357_2.nsv", "result1357_3.nsv", "result1357_4.nsv", "result1357_5.nsv", "result1357_6.nsv", "result1357_7.nsv"];
val thyn = "vfmTestDefs1357";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
