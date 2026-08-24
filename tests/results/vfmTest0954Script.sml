Theory vfmTest0954[no_sig_docs]
Ancestors vfmTestDefs0954
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0954_0.nsv", "result0954_1.nsv", "result0954_2.nsv"];
val thyn = "vfmTestDefs0954";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
