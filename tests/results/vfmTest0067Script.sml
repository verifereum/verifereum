Theory vfmTest0067[no_sig_docs]
Ancestors vfmTestDefs0067
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0067_0.nsv", "result0067_1.nsv"];
val thyn = "vfmTestDefs0067";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
