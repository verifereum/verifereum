Theory vfmTest0043[no_sig_docs]
Ancestors vfmTestDefs0043
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0043_0.nsv", "result0043_1.nsv", "result0043_2.nsv", "result0043_3.nsv"];
val thyn = "vfmTestDefs0043";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
